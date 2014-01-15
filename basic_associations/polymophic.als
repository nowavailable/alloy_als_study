module polymophic_association

abstract sig Kind {}
sig UserProfile extends Kind { 
  photo: disj one Photo
}
sig Album extends Kind {
  photos: disj set Photo
}

sig Photo { 
  photoable_type: one PhotoableTypeField,
  photoable: one Photoable
}

abstract sig PhotoableTypeField {
  parent: one Photo
}
sig UserProfile_Photoable extends PhotoableTypeField { 
  user_profile: disj one UserProfile
}
sig Album_Photoable extends PhotoableTypeField { 
  album: some Album
}

sig Photoable in Kind {}

fact {
  // 相互的関係
  Photo <: photoable_type = ~(PhotoableTypeField <: parent)
  UserProfile <: photo = ~(Photo <: photoable_type.user_profile)
  Album <: photos = ~(Photo <: photoable_type.album)

  Photo <: photoable in ~(UserProfile <: photo) + ~(Album <: photos)
}
run {} // for 4 but 8 Photo
